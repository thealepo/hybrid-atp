# Vercel Deployment Guide

This guide will help you deploy the Hybrid ATP application to Vercel.

## Prerequisites

1. A [Vercel account](https://vercel.com/signup) (free tier works)
2. [Vercel CLI](https://vercel.com/docs/cli) installed (optional but recommended)
3. A HuggingFace API token with access to the required models

## Quick Deployment Options

### Option 1: Deploy via Vercel Dashboard (Easiest)

1. **Push your code to GitHub**
   ```bash
   git init
   git add .
   git commit -m "Initial commit for Hybrid ATP"
   git branch -M main
   git remote add origin <your-github-repo-url>
   git push -u origin main
   ```

2. **Import to Vercel**
   - Go to [Vercel Dashboard](https://vercel.com/dashboard)
   - Click "Add New Project"
   - Import your GitHub repository
   - Vercel will auto-detect the Python/Flask application

3. **Configure Environment Variables**
   - In the project settings, go to "Environment Variables"
   - Add: `HUGGINGFACE_TOKEN` with your HuggingFace API token
   - Click "Deploy"

### Option 2: Deploy via Vercel CLI

1. **Install Vercel CLI**
   ```bash
   npm install -g vercel
   ```

2. **Login to Vercel**
   ```bash
   vercel login
   ```

3. **Deploy from project directory**
   ```bash
   cd c:\Users\brand\Downloads\atphybrid\hybrid-atp
   vercel
   ```

4. **Follow the prompts:**
   - Set up and deploy? **Y**
   - Which scope? Select your account
   - Link to existing project? **N**
   - What's your project's name? `hybrid-atp` (or your preferred name)
   - In which directory is your code located? `./`
   - Want to override settings? **N**

5. **Add environment variable**
   ```bash
   vercel env add HUGGINGFACE_TOKEN
   ```
   - Select Production, Preview, and Development
   - Paste your HuggingFace token

6. **Redeploy with environment variable**
   ```bash
   vercel --prod
   ```

## Important Notes

### Model Loading Considerations

⚠️ **Important**: Vercel has limitations for serverless functions:
- **Maximum execution time**: 10 seconds (Hobby), 60 seconds (Pro)
- **Memory limit**: 1024 MB (Hobby), 3008 MB (Pro)
- **Cold start**: Models will reload on each cold start

Due to these limitations, the full model loading might timeout. Consider these alternatives:

1. **Use lighter models or API-only endpoints**
2. **Deploy the ML backend separately** (e.g., Hugging Face Spaces, AWS Lambda with higher limits)
3. **Upgrade to Vercel Pro** for longer execution times

### Recommended Architecture for Production

For better performance, split the architecture:

```
Frontend (Vercel)          Backend API (HF Spaces/AWS)
   ↓                              ↓
  Web UI  ──────requests───→  ML Models
(app.py routes)            (LeanGenerator, MathReasoner)
```

To implement this:
1. Deploy the ML models to Hugging Face Spaces or a dedicated server
2. Update `app.py` to call the external API instead of loading models locally
3. Keep the frontend on Vercel

## Testing Your Deployment

After deployment, you'll get a URL like: `https://hybrid-atp.vercel.app`

1. Visit the URL
2. Test with the example theorems
3. Check the `/health` endpoint: `https://your-app.vercel.app/health`

## Troubleshooting

### Deployment Times Out
- The models are too large for serverless
- Solution: Use external ML API or upgrade to Vercel Pro

### 404 Error
- Check that `vercel.json` routing is correct
- Ensure `app.py` is in the root directory

### Environment Variable Not Found
- Verify `HUGGINGFACE_TOKEN` is set in Vercel dashboard
- Redeploy after adding environment variables

### Import Errors
- Ensure all dependencies are in `requirements.txt`
- Check Python version compatibility (Vercel uses Python 3.9 by default)

## Files Added for Deployment

- **vercel.json**: Configuration for Vercel platform
- **.vercelignore**: Files to exclude from deployment
- **DEPLOYMENT.md**: This deployment guide

## Local Testing

Test the deployment setup locally:

```bash
# Install dependencies
pip install -r requirements.txt

# Run the app
python app.py

# Visit http://127.0.0.1:5000
```

## Next Steps

1. **Monitor your deployment** in the Vercel dashboard
2. **Set up custom domain** (optional) in project settings
3. **Enable analytics** to track usage
4. **Consider implementing caching** for frequently used theorems

## Alternative Deployment Platforms

If Vercel doesn't work due to model size limitations, consider:

- **Hugging Face Spaces** (supports larger models, GPU)
- **Railway.app** (more flexible Python deployments)
- **Google Cloud Run** (pay-per-use, higher limits)
- **AWS Lambda with API Gateway** (configurable memory/timeout)
- **DigitalOcean App Platform** (simple container deployment)

## Support

For issues:
- Check [Vercel Documentation](https://vercel.com/docs)
- Review [Vercel Python Runtime](https://vercel.com/docs/functions/serverless-functions/runtimes/python)
- Open an issue in your repository
